package sdql.backend

import sdql.analysis.TypeInference
import sdql.ir.*
import sdql.raise

object MlirCodegen {
  type TypesCtx = TypeInference.Ctx

  def mlirType(typ: Type): String =
    typ match {
      case RealType                              => "f64"
      case BoolType                              => "i1"
      case IntType                               => "i32"
      case LongType                              => "i64"
      case DateType                              => "i32"
      case DictType(keyT: Type, valueT: Type, _) =>
        s"dictionary<${mlirType(keyT)}, ${mlirType(valueT)}>"
      case RecordType(attrs: Seq[Attribute])     =>
        val attrsTyped = attrs.map(attr => s"\"${attr.name}\" : ${mlirType(attr.tpe)}")
        attrsTyped.mkString("record<", ", ", ">")
      case StringType(Some(maxLen))              => s"memref<${maxLen}xi8>"
      case StringType(None)                      => s"memref<?xi8>"
      case _                                     => raise(f"unhandled type $typ in MlirCodegen.mlirType()")
    }

  final case class V(name: String, typ: Type)

  final class MlirBuilder {
    private var i           = 0
    private val out         = Vector.newBuilder[String]
    private var indentLevel = 0

    def result: Vector[String] = out.result()

    def line(s: String): Unit = {
      val indent = "  " * indentLevel
      out += indent + s
    }

    def fresh(prefix: String = "%t"): String = {
      val res = s"${prefix}_$i"
      i += 1
      res
    }

    def withIndent[A](k: => A): A = {
      indentLevel += 1
      val r = k
      indentLevel -= 1
      r
    }
  }

  def run(e: Exp): Vector[String] = {
    // val builder = new MlirBuilder
    val ctx     = Map.empty[Sym, Type]
    val builder = new MlirBuilder

    bindToName(e, None, expectedType = None)(ctx, builder)

    genRangeBuiltin ++ builder.result
  }

  def bindToName(x: Exp, desired: Option[String], expectedType: Option[Type] = None)(implicit
    ctx: TypesCtx,
    builder: MlirBuilder
  ): V =
    x match {
      // let x = e1 in e2
      case LetBinding(x @ Sym(name), e1, e2) =>
        val boundName = s"%$name"
        val rhs       = bindToName(e1, desired = Some(boundName), expectedType = None)

        val ctx2 = ctx ++ Map(x -> rhs.typ)
        bindToName(e2, desired = None, expectedType = None)(ctx2, builder)

      case sym @ Sym(name) =>
        val tpe = ctx.getOrElse(sym, raise(s"unknown name for symbol: $sym"))
        V(s"%$name", tpe)

      case Const(v: Int) =>
        val name = desired.getOrElse(builder.fresh("%consti"))
        builder.line(s"$name = \"arith.constant\"() <{value = $v : i32}> : () -> i32")
        V(name, IntType)
      // type of cmp is the same as type of result! no need to look at args

      case Const(v: Double) =>
        val name = desired.getOrElse(builder.fresh("%constd"))
        builder.line(
          s"$name = \"arith.constant\"() <{value = ${if (v.toString == "0") "0.0" else v}  : f64}> : () -> f64"
        )
        V(name, RealType)

      case Const(v: Boolean)   =>
        val name = desired.getOrElse(builder.fresh("%constv"))
        builder.line(s"$name = \"arith.constant\"() <{value = ${if (v) 1 else 0} : i1}> : () -> i1")
        V(name, BoolType)

      // TODO: what's mlir handling of date? for now its i32
      case Const(v: DateValue) =>
        val name = desired.getOrElse(builder.fresh("%constda"))
        builder.line(s"$name = \"arith.constant\"() <{value = ${v.v} : i32}> : () -> i32")
        V(name, DateType)

      case Const(v: String)                             =>
        val name = desired.getOrElse(builder.fresh("%constds"))
        // StringType(Some(maxLen: Int)) or StringType(None)
        val tpe  = TypeInference.run(x)

        builder.line(s"// $v")
        // TODO: handle encoding stuff
        builder.line(
          s"$name = \"arith.constant\"() <{value = dense<${v.getBytes().mkString("[", ", ", "]")}> : ${mlirType(tpe)}}> : () -> ${mlirType(tpe)}"
        )
        V(name, tpe)

      // ex: %dict = sdql.empty_dictionary : dictionary<i32, f16>
      case DictNode(Nil, _)                             =>
        expectedType match {
          case Some(typ) =>
            val name = desired.getOrElse(builder.fresh("%dict"))
            builder.line(s"$name = sdql.empty_dictionary : ${mlirType(typ)}")
            V(name, typ)
          case None      =>
            raise("empty dictionary needs expected DictType")
        }

      // ex: %8 = sdql.create_dictionary %5, %7 : i32, i1 -> dictionary<i32, i1>
      case DictNode(args: Seq[(Exp, Exp)], _: DictHint) =>
        val name = desired.getOrElse(builder.fresh("%dict"))

        val resultTyp = TypeInference.run(x)(ctx)

        // Seq of all args (keys and values)
        val allArgs     = args.flatMap { case (key, value) => Seq(key, value) }
        // types of arg list
        val argTypes    = allArgs
          .map(argTyp => mlirType(TypeInference.run(argTyp)(ctx)))
          .mkString(", ")
        // compute arguments and retrieve names
        val computeArgs = allArgs.map(bindToName(_, None))

        val argOps = computeArgs.map(_.name).mkString(", ")
        builder.line(s"$name = sdql.create_dictionary $argOps : $argTypes -> ${mlirType(resultTyp)}")
        V(name, resultTyp)

      case Get(e1: Exp, e2: Exp) =>
        val name      = desired.getOrElse(builder.fresh("%get"))
        val resultTyp = TypeInference.run(x)(ctx)

        val where = bindToName(e1, None, None)
        val what  = bindToName(e2, None, None)

        where.typ match {
          case d: DictType   =>
            builder.line(
              s"$name = sdql.lookup_dictionary ${where.name} [${what.name} : ${mlirType(what.typ)}] : ${mlirType(d)} -> ${mlirType(resultTyp)}"
            )
          case r: RecordType =>
            builder.line(
              s"$name = sdql.access_record ${where.name} \"${what.name}\" : ${mlirType(r)} -> ${mlirType(resultTyp)}"
            )
          case x             => raise("dictionary expected on lhs of get, instead got: " + x.simpleName)
        }
        V(name, resultTyp)

      // ex: %val = sdql.lookup_dictionary %dict [%key : i32] : dictionary<i32, f16> -> f16

      case Load(path: String, typ: Type, _: DictNode)                                            =>
        // TODO: handle skiplist
        val name = desired.getOrElse(builder.fresh("%load"))
        builder.line(s"$name = sdql.load \"$path\" : ${mlirType(typ)}")
        V(name, TypeInference.run(x))

      // sum (x in e1) body

      // %0 = sdql.empty_dictionary : dictionary<i32, f16>

      // %1 = sdql.sum %0 : dictionary<i32, f16> -> f16 {
      // ^bb0(%x: record<"key": i32, "value": f16>):
      //   %tmp = sdql.access_record %x "value" : record<"key": i32, "value": f16> -> f16
      //   sdql.yield %tmp : f16
      // }
      case Sum(key: Sym, value: Sym, e1: Exp, body: Exp)                                         =>
        // key and value present in body but not in e1
        val e1Evaled = bindToName(e1, None, None)

        val name    = desired.getOrElse(builder.fresh("%sum"))
        val retType = TypeInference.run(x)
        builder.line(s"$name = sdql.sum ${e1Evaled.name} : ${mlirType(e1Evaled.typ)} -> ${mlirType(retType)} {")

        // result type? its type of body assuming proper binding key and value
        val extendedCtx = TypeInference.run(e1) match {
          case DictType(dictKey: Type, dictVal: Type, _) =>
            ctx ++ Map(key -> dictKey, value -> dictVal)
          case x                                         =>
            raise(f"unhandled sum on type ${x.prettyPrint} in MlirCodegen.bindToName()")
        }

        val bodyRetTyp = TypeInference.run(body)(extendedCtx)

        val blockName = builder.fresh("^bb")
        builder.line(
          s"${blockName}(%${key.name}: ${mlirType(extendedCtx.get(key).get)}, %${value.name}: ${mlirType(extendedCtx.get(value).get)}):"
        )
        builder.withIndent {
          val blockBody = bindToName(body, None, None)(extendedCtx, builder)
          builder.line(s"sdql.yield ${blockBody.name} : ${mlirType(bodyRetTyp)}")
        }
        builder.line("}")
        V(name, retType)

      // %res = sdql.create_record {fields = ["a", "b"]} %0, %1 : i32, f32 -> record<"a": i32, "b": f32>
      case RecNode(values)                                                                       =>
        val fieldTypes = values.map(_._2).map(TypeInference.run(_))
        val fieldNames = values.map(_._1)

        val computedFields     = values.map(_._2).map(bindToName(_, None))
        val computedFieldTypes = fieldTypes.map(mlirType(_))

        val name = desired.getOrElse(builder.fresh("%recnode"))

        val fieldsAttr = s"{fields = ${fieldNames.map(name => s"\"$name\"").mkString("[", ", ", "]")}}"

        val retTypeFields = values
          .map(field => s"\"${field._1}\": ${mlirType(TypeInference.run(field._2))}")
          .mkString("record<", ", ", ">")

        builder.line(
          s"$name = sdql.create_record $fieldsAttr ${computedFields.map(_.name).mkString(", ")} : ${computedFieldTypes
              .mkString(", ")} -> $retTypeFields"
        )
        V(name, TypeInference.run(x))

      // %val = sdql.access_record %rec "a" : record<"a": i32, "b": f32> -> i32
      case FieldNode(e: Exp, f: String)                                                          =>
        val inType            = TypeInference.run(e) match {
          case x @ RecordType(_) => x
          case x @ _             => raise(f"unhandled field access on type ${x.prettyPrint} in MlirCodegen.bindToName()")
        }
        val accessedFieldType = inType.attrs.find(_.name == f) match {
          case Some(attr) => attr.tpe
          case None       =>
            raise(
              f"unhandled field access due to missing field $f in ${inType.prettyPrint} in MlirCodegen.bindToName()"
            )
        }
        val retTypeFields     =
          inType.attrs.map(field => s"\"${field.name}\": ${mlirType(field.tpe)}").mkString("record<", ", ", ">")

        val compE = bindToName(e, None)

        val name = desired.getOrElse(builder.fresh("%fieldnode"))
        builder.line(
          s"$name = sdql.access_record ${compE.name} \"$f\" : $retTypeFields -> ${mlirType(accessedFieldType)}"
        )

        V(name, accessedFieldType)

      // %0 = "func.call"(%1) <{callee = @range_builtin}> : (i32) -> dictionary<i32, i1>
      case RangeNode(e: Exp)                                                                     =>
        val compE = bindToName(e, None)
        val name  = desired.getOrElse(builder.fresh("%rangenode"))
        val typ   = TypeInference.run(e)

        builder.line(
          s"$name = \"func.call\"(${compE.name}) <{callee = @range_builtin}> : (${mlirType(typ)}) -> dictionary<${mlirType(typ)}, i32>"
        )
        V(name, TypeInference.run(x))

      /*
  %res = "scf.if"(%cond) ({
      ...
      "scf.yield"(%mul) : (f64) -> ()
  }, {
      ...
      "scf.yield"(%zero) : (f64) -> ()
  }) : (i1) -> f64
       */
      case IfThenElse(cond, thenp, elsep)                                                        =>
        // compute result type
        val outTyp = TypeInference.run(x)

        // lower the condition
        val c = bindToName(cond, None)
        if (c.typ != BoolType) {
          raise(s"condition in IfThenElse must be of type BoolType, got ${c.typ.prettyPrint}")
        }

        val name = desired.getOrElse(builder.fresh("%if"))

        // emit if header
        builder.line(s"$name = \"scf.if\"(${c.name}) ({")

        // emit then branch
        builder.withIndent {
          val thenBranch = bindToName(thenp, desired = None, expectedType = Some(outTyp))
          val upcasted = upcastTo(thenBranch, outTyp)
          builder.line(s"\"scf.yield\"(${upcasted.name}) : (${mlirType(outTyp)}) -> ()")
        }
        builder.line("}, {")

        // emit else branch
        builder.withIndent {
          val elseBranch = bindToName(elsep, desired = None, expectedType = Some(outTyp))
          val upcasted = upcastTo(elseBranch, outTyp)
          builder.line(s"\"scf.yield\"(${upcasted.name}) : (${mlirType(outTyp)}) -> ()")
        }

        builder.line(s"}) : (i1) -> ${mlirType(outTyp)}")
        V(name, outTyp)

      // %2 = "arith.cmpi"(%0, %1) <{predicate = 3}> : (i32, i32) -> i1
      case Cmp(e1, e2, cmp) if List(IntType, LongType, DateType).contains(TypeInference.run(e1)) =>
        val outTyp = TypeInference.run(x)
        val outT   = mlirType(outTyp)

        val predicateVal = cmp match {
          // https://mlir.llvm.org/docs/Dialects/ArithOps/#cmpipredicate
          case "<=" => 3
          case "<"  => 2
          case "==" => 0
          case "!=" => 1
        }
        val comp1        = bindToName(e1, None)
        val typ1         = TypeInference.run(e1)
        val t1           = mlirType(typ1)
        val comp2        = bindToName(e2, None, Some(typ1))
        val t2           = mlirType(comp2.typ)

        val name = desired.getOrElse(builder.fresh("%cmpi"))

        builder.line(
          s"$name = \"arith.cmpi\"(${comp1.name}, ${comp2.name}) <{predicate = $predicateVal}> : ($t1, $t2) -> $outT"
        )
        V(name, outTyp)

      case Cmp(e1, e2, cmp) if TypeInference.run(e1) == RealType                            =>
        // is it always i1?
        val outTyp = TypeInference.run(x)
        val outT   = mlirType(outTyp)

        val predicateVal = cmp match {
          // https://mlir.llvm.org/docs/Dialects/ArithOps/#cmpfpredicate
          case "<=" => 5
          case "<"  => 4
          case "!=" => 6
          case "==" => 1
        }
        val comp1        = bindToName(e1, None)
        val typ1         = TypeInference.run(e1)
        val t1           = mlirType(typ1)
        val comp2        = bindToName(e2, None, Some(typ1))
        val t2           = mlirType(comp2.typ)

        val name = desired.getOrElse(builder.fresh("%cmpf"))

        builder.line(
          s"$name = \"arith.cmpf\"(${comp1.name}, ${comp2.name}) <{fastmath = #arith.fastmath<none>, predicate = $predicateVal}> : ($t1, $t2) -> $outT"
        )
        V(name, outTyp)

      // %a = arith.muli %b, %c : i64
      case Mult(e1, e2) if List(IntType, LongType, DateType).contains(TypeInference.run(x)) =>
        val outTyp = TypeInference.run(x)
        val outT   = mlirType(outTyp)

        val name = desired.getOrElse(builder.fresh("%multi"))

        val comp1 = bindToName(e1, None)
        val t1    = mlirType(TypeInference.run(e1))
        val comp2 = bindToName(e2, None)
        val t2    = mlirType(TypeInference.run(e2))

        builder.line(s"$name = \"arith.muli\"(${comp1.name}, ${comp2.name}) : ($t1, $t2) -> $outT")
        V(name, outTyp)

      case Mult(e1, e2) if TypeInference.run(x) == RealType =>
        val outTyp = TypeInference.run(x)
        val outT   = mlirType(outTyp)

        val name = desired.getOrElse(builder.fresh("%multf"))

        val comp1 = bindToName(e1, None)
        val t1    = mlirType(TypeInference.run(e1))
        val comp2 = bindToName(e2, None)
        val t2    = mlirType(TypeInference.run(e2))

        builder.line(
          s"$name = \"arith.mulf\"(${comp1.name}, ${comp2.name}) <{fastmath = #arith.fastmath<none>}> : ($t1, $t2) -> $outT"
        )
        V(name, outTyp)

      case Add(e1, e2) if List(IntType, LongType).contains(TypeInference.run(x)) =>
        val outTyp = TypeInference.run(x)
        val outT   = mlirType(outTyp)

        val name = desired.getOrElse(builder.fresh("%addi"))

        val comp1 = bindToName(e1, None)
        val comp2 = bindToName(e2, None)

        // operands need to be of the same type
        val lhs = upcastTo(comp1, outTyp)
        val rhs = upcastTo(comp2, outTyp)

        builder.line(s"$name = \"arith.addi\"(${lhs.name}, ${rhs.name}) : ($outT, $outT) -> $outT")
        V(name, outTyp)

      case Add(e1, e2) if TypeInference.run(x) == RealType =>
        val outTyp = TypeInference.run(x)
        val outT   = mlirType(outTyp)

        val name = desired.getOrElse(builder.fresh("%addf"))

        val comp1 = bindToName(e1, None)
        val comp2 = bindToName(e2, None)

        // operands need to be of the same type
        val lhs = upcastTo(comp1, outTyp)
        val rhs = upcastTo(comp2, outTyp)

        builder.line(
          s"$name = \"arith.addf\"(${lhs.name}, ${rhs.name}) <{fastmath = #arith.fastmath<none>}> : ($outT, $outT) -> $outT"
        )
        V(name, outTyp)

      case Neg(e) if TypeInference.run(e) == BoolType =>
        val zero = desired.getOrElse(builder.fresh("%zero"))

        // val res = s"$name = \"arith.constant\"() <{value = $v : i32}> : () -> i32"

        val name = desired.getOrElse(builder.fresh("%neg"))

        val comp = bindToName(e, None)
        builder.line(s"$zero = \"arith.constant\"() <{value = 0 : i1}> : () -> i1")

        builder.line(s"$name = \"arith.cmpi\"(${comp.name}, $zero) <{predicate = 0}> : (i1, i1) -> i1")
        V(name, BoolType)

      case Neg(e) if List(IntType, LongType).contains(TypeInference.run(e)) =>
        val outTyp = TypeInference.run(x)
        val name   = desired.getOrElse(builder.fresh("%negi"))

        val comp = bindToName(e, None)
        val t    = mlirType(outTyp)

        val zero = desired.getOrElse(builder.fresh("%zero"))
        builder.line(s"$zero = \"arith.constant\"() <{value = 0 : $t}> : () -> $t")

        builder.line(s"$name = \"arith.subi\"($zero, ${comp.name}) : ($t, $t) -> $t")
        V(name, outTyp)

      case Neg(e) if TypeInference.run(x) == RealType =>
        val name = desired.getOrElse(builder.fresh("%negf"))

        val comp = bindToName(e, None)
        val t    = mlirType(TypeInference.run(e))

        val zero = desired.getOrElse(builder.fresh("%zero"))
        builder.line(s"$zero = \"arith.constant\"() <{value = 0.0 : $t}> : () -> $t")

        builder.line(
          s"$name = \"arith.subf\"($zero, ${comp.name}) <{fastmath = #arith.fastmath<none>}> : ($t, $t) -> $t"
        )
        V(name, RealType)

      case Concat(e1, e2)
          if TypeInference.run(e1).isInstanceOf[RecordType] && TypeInference.run(e2).isInstanceOf[RecordType] =>
        val outTyp = TypeInference.run(x)

        val typ1 = mlirType(TypeInference.run(e1))
        val typ2 = mlirType(TypeInference.run(e2))

        val gen1 = bindToName(e1, None)
        val gen2 = bindToName(e2, None)

        val name = desired.getOrElse(builder.fresh("%concat"))

        builder.line(s"$name = sdql.concat ${gen1.name}, ${gen2.name} : $typ1, $typ2 -> ${mlirType(outTyp)}")
        V(name, outTyp)

      case External(extName, args) =>
        val outT = TypeInference.run(x)

        val generated = args.map(bindToName(_, None))
        val types     = args.map(TypeInference.run)

        val name = desired.getOrElse(builder.fresh("%external"))

        builder.line(
          s"$name = sdql.external \"$extName\", ${generated.map(_.name).mkString(", ")} : ${types.map(mlirType).mkString(", ")} -> ${mlirType(outT)}"
        )
        V(name, outT)

      case Cmp(e1, e2, cmp) if cmp == "==" =>
        val outTyp = TypeInference.run(x)

        val typ1 = mlirType(TypeInference.run(e1))
        val typ2 = e2 match {
          // workaround for `a != { }`
          case DictNode(Nil, _) => typ1
          case _                => mlirType(TypeInference.run(e2))
        }

        val gen1 = bindToName(e1, None)
        // workaround for a != { }
        val gen2 = bindToName(e2, None, expectedType = Some(TypeInference.run(e1)))

        val name = desired.getOrElse(builder.fresh("%cmp"))

        builder.line(s"$name = sdql.cmp ${gen1.name}, ${gen2.name} : $typ1, $typ2 -> ${mlirType(outTyp)}")
        V(name, outTyp)

      case Cmp(e1, e2, cmp) if cmp == "!=" =>
        val negated = Cmp(e1, e2, "==")
        bindToName(Neg(negated), desired, expectedType)

      // TODO: what does it exactly do?
      case Unique(e)                       =>
        val outTyp = TypeInference.run(x)

        val name = desired.getOrElse(builder.fresh("%uniq"))

        val gen   = bindToName(e, None, None)
        val inTyp = gen.typ

        builder.line(s"$name = sdql.unique ${gen.name} : ${mlirType(inTyp)} -> ${mlirType(outTyp)}")
        V(name, TypeInference.run(x))

      case _ =>
        raise("¯\\_(ツ)_/¯ " + x)
    }

  private def upcastTo(v: V, target: Type)(implicit builder: MlirBuilder): V =
    (v.typ, target) match {
      case (IntType, LongType) =>
        val name = builder.fresh("%extsi")
        builder.line(s"$name = \"arith.extsi\"(${v.name}) : (i32) -> i64")
        V(name, LongType)

      case (IntType, RealType) =>
        val name = builder.fresh("%sitofp")
        builder.line(s"$name = \"arith.sitofp\"(${v.name}) : (i32) -> f64")
        V(name, RealType)

      case (LongType, RealType) =>
        val name = builder.fresh("%sitofp")
        builder.line(s"$name = \"arith.sitofp\"(${v.name}) : (i64) -> f64")
        V(name, RealType)

      // TODO handle DateType (acts like i32)

      case (from, to)           =>
        if (from == to) v else raise(s"no supported upcast from ${from.prettyPrint} to ${to.prettyPrint}")
    }

  def genRangeBuiltin: Vector[String] =
    Vector(
      "func.func @range_builtin(%n: i32) -> dictionary<i32, i32> {",
      "  %zero = \"arith.constant\"() <{value = 0}> : () -> i32",
      "  %is_terminal = \"arith.cmpi\"(%n, %zero) <{\"predicate\" = 3}> : (i32, i32) -> i1",
      "  %res = \"scf.if\"(%is_terminal) ({",
      "    %empty = sdql.empty_dictionary : dictionary<i32, i32>",
      "    \"scf.yield\"(%empty) : (dictionary<i32, i32>) -> ()",
      "  }, {",
      "    %one = \"arith.constant\"() <{value = 1}> : () -> i32",
      "    %smaller_n = \"arith.subi\"(%n, %one) : (i32, i32) -> i32",
      "    %prev_range = \"func.call\"(%smaller_n) <{callee = @range}> : (i32) -> dictionary<i32, i32>",
      "    %true = \"arith.constant\"() <{value = 1}> : () -> i32",
      "    %extension = sdql.create_dictionary %smaller_n, %true : i32, i32 -> dictionary<i32, i32>",
      "",
      "    // return %extension + %prev_range",
      "    %added = sdql.dictionary_add %extension %prev_range : dictionary<i32, i32>, dictionary<i32, i32> -> dictionary<i32, i32>",
      "    \"scf.yield\"(%added) : (dictionary<i32, i32>) -> ()",
      "  }) : (i1) -> dictionary<i32, i32>",
      "  func.return %res : dictionary<i32, i32>",
      "}"
    )

}
