package sdql.backend

import sdql.analysis.TypeInference
import sdql.ir.*
import sdql.raise

object MlirCodegen {
  type TypesCtx = TypeInference.Ctx

  def mlirType(typ: Type): String =
    typ match {
        case RealType => "f64"
        case BoolType => "i1"
        case IntType => "i32"
        case LongType => "i64"
        case DateType => "i32"
        case DictType(keyT: Type, valueT: Type, _) =>
            s"dictionary<${mlirType(keyT)}, ${mlirType(valueT)}>"
        case RecordType(attrs: Seq[Attribute]) => {
            val attrsTyped = attrs.map(attr => s"\"${attr.name}\" : ${mlirType(attr.tpe)})")
            attrsTyped.mkString("record<", ", ", ">")
        }
        case StringType(Some(maxLen)) => s"memref<${maxLen}xi8>"
        case StringType(None) => s"memref<?xi8>" 
        case _ => raise(f"unhandled type $typ in MlirCodegen.mlirType()")
    }

  private final class Fresh {
    private var i = 0
    def next(prefix: String): String = {
        val res = s"${prefix}_$i"
        i = i + 1
        res
    }
  }

  private val fresh = new Fresh

  case class Emitted(code: Vector[String], value: String)

  def run(e: Exp): Emitted = {
    def bindToName(x: Exp, desired: Option[String], expected: Option[Type] = None)(implicit ctx : TypesCtx): Emitted = x match {
      // let x = e1 in e2
      case LetBinding(x @ Sym(name), e1, e2) => {
        val boundName = s"%$name"
        val rhs = bindToName(e1, Some(boundName))
        val ctx2 = ctx ++ Map(x -> TypeInference.run(e1)(ctx))
        val body = bindToName(e2, None)(ctx2)
        Emitted(rhs.code ++ body.code, body.value)
      }

      case Sym(name) => {
        val res = s"%$name"
        Emitted(Vector.empty, res)
      }

      case Const(v: Int) => {
        val binding = desired.getOrElse(fresh.next("%consti"))
        val res = s"$binding = \"arith.constant\"() <{value = $v : i32}> : () -> i32"
        Emitted(Vector(res), binding)
      }

      case Const(v: Double) => {
        val binding = desired.getOrElse(fresh.next("%constd"))
        val res = s"$binding = \"arith.constant\"() <{value = $v : f64}> : () -> f64"
        Emitted(Vector(res), binding)
      }

      case Const(v: Boolean) => {
        val binding = desired.getOrElse(fresh.next("%constb"))
        val res = s"$binding = \"arith.constant\"() <{value = ${if(v) 1 else 0} : i1}> : () -> i1"
        Emitted(Vector(res), binding)
      }

      // TODO: what's mlir handling of date? for now its i32
      case Const(v: DateValue) => {
        val binding = desired.getOrElse(fresh.next("%constda"))
        val res = s"$binding = \"arith.constant\"() <{value = ${v.v} : i32}> : () -> i32"
        Emitted(Vector(res), binding)
      }

      case Const(v: String) => {
        val binding = desired.getOrElse(fresh.next("%consts"))
        val res = s"$binding = \"arith.constant\"() <{value = dense<[${v.getBytes().mkString("[", ", ", "]")}]}> : () -> memref<${v.size}xi1>"
        Emitted(Vector(res), binding)
      }

      // ex: %dict = sdql.empty_dictionary : dictionary<i32, f16>
      case DictNode(Nil, _) => {
        // TODO: handle empty dict (currently type inference breaks)
        // raise(f"unhandled empty dictionary in MlirCodegen.bindToName()")

        val typ = mlirType(expected.get)
        val binding = desired.getOrElse(fresh.next("%dict"))
        Emitted(Vector(s"$binding = sdql.empty_dictionary : $typ"), binding)
      }

      // ex: %8 = sdql.create_dictionary %5, %7 : i32, i1 -> dictionary<i32, i1>
      case DictNode(args: Seq[(Exp, Exp)], _: DictHint) => {
        val resultTyp = mlirType(TypeInference.run(x)(ctx))
        val allArgs = args.flatMap { case (key, value) => Seq(key, value) }
        val argTypes = allArgs.map { argTyp => mlirType(TypeInference.run(argTyp)(ctx))}.mkString(", ")

        val binding = desired.getOrElse(fresh.next("%dict"))

        val convertedArgs = allArgs.map(bindToName(_, None))
        val argOps = convertedArgs.map(_.value).mkString(", ")
        Emitted(convertedArgs.flatMap(_.code).toVector ++ Vector(s"$binding = sdql.create_dictionary $argOps : $argTypes -> $resultTyp"), binding)
      }
        
      case Get(e1: Exp, e2: Exp) => {
        val where = bindToName(e1, None)

        val what = bindToName(e2, None)

        val binding = desired.getOrElse(fresh.next("%get"))

        TypeInference.run(e1) match {
            case recType: RecordType => {
              // %val = sdql.access_record %rec "a" : record<"a": i32, "b": f32> -> i32 
              val res = s"$binding = sdql.access_record ${where.value} \"${what.value}\" : ${recType.attrs.map(attr => s"${attr.name}: ${mlirType(attr.tpe)}").mkString("record<", ", ", ">")}"
              Emitted(where.code ++ what.code ++ Vector(res), binding)
            }
            case dictType: DictType => {
              // ex: %val = sdql.lookup_dictionary %dict [%key : i32] : dictionary<i32, f16> -> f16
              val res = s"$binding = sdql.lookup_dictionary ${where.value} [${what.value} : ${mlirType(TypeInference.run(e2))}] : ${mlirType(dictType)} -> ${mlirType(dictType.value)}"
              Emitted(where.code ++ what.code ++ Vector(res), binding)
            }
            case x => {
              raise(f"unhandled lookup on type ${x.prettyPrint} in MlirCodegen.bindToName()")
            }
        }
      }

      case Load(_: String, _: Type, _: DictNode) => {
        val binding = desired.getOrElse(fresh.next("%load"))
        Emitted(Vector(s"$binding = load shananigans"), binding)
      }

      // sum (x in e1) body

      // %0 = sdql.empty_dictionary : dictionary<i32, f16>

      // %1 = sdql.sum %0 : dictionary<i32, f16> -> f16 {
      // ^bb0(%x: record<"key": i32, "value": f16>):
      //   %tmp = sdql.access_record %x "value" : record<"key": i32, "value": f16> -> f16
      //   sdql.yield %tmp : f16
      // }
      case Sum(key: Sym, value: Sym, e1: Exp, body: Exp) => {
        // key and value present in body but not in e1
        val e1Evaled = bindToName(e1, None)

        val binding = desired.getOrElse(fresh.next("%sum"))

        val prefix = s"$binding = sdql.sum ${e1Evaled.value} : ${mlirType(TypeInference.run(e1))}"

        // result type? its type of body assuming proper binding key and value
        val extendedCtx = TypeInference.run(e1) match {
            case DictType(dictKey: Type, dictVal: Type, _) =>
                ctx ++ Map(key -> dictKey, value -> dictVal)
            case x =>
              raise(f"unhandled sum on type ${x.prettyPrint} in MlirCodegen.bindToName()")
        }

        val retType = mlirType(TypeInference.run(body)(extendedCtx))

        val blockDecl = s"${fresh.next("^bb")}(%${key.name}: ${mlirType(extendedCtx.get(key).get)}, %${value.name}: ${mlirType(extendedCtx.get(value).get)}):"
        val blockBody = bindToName(body, None)(extendedCtx)
        val blockRet = s"  sdql.yield ${blockBody.value} : ${retType}"

        // here we assume result of aggregation of elements of type retType is retType
        val newOp = Vector(s"$prefix -> $retType {") ++ Vector(blockDecl) ++ blockBody.code.map("  " + _) ++ Vector(blockRet) ++ Vector("}")
        Emitted(e1Evaled.code ++ newOp, "binding")
      }
      
      // %res = sdql.create_record {fields = ["a", "b"]} %0, %1 : i32, f32 -> record<"a": i32, "b": f32>
      case RecNode(values) => {
        val fieldTypes = values.map(_._2).map(TypeInference.run(_))
        val fieldNames = values.map(_._1)

        val computedFields = values.map(_._2).map(bindToName(_, None))
        val computedFieldTypes = fieldTypes.map(mlirType(_))

        val binding = desired.getOrElse(fresh.next("%recnode"))

        val fieldsAttr = s"{fields = ${fieldNames.map(name => s"\"$name\"").mkString("[", ", ", "]")}}"
        
        val retTypeFields = values.map(field => s"\"${field._1}\": ${mlirType(TypeInference.run(field._2))}").mkString("record<", ", ", ">")

        val op = s"$binding = sdql.create_record $fieldsAttr ${computedFields.map(_.value).mkString(", ")} : ${computedFieldTypes.mkString(", ")} -> $retTypeFields"
        Emitted(computedFields.flatMap(_.code).toVector ++ Vector(op), binding)
      }
        
      // %val = sdql.access_record %rec "a" : record<"a": i32, "b": f32> -> i32
      case FieldNode(e: Exp, f: String) => {
        val inType = TypeInference.run(e) match {
            case x @ RecordType(_) => x
            case x @ _ => raise(f"unhandled field access on type ${x.prettyPrint} in MlirCodegen.bindToName()")
        }
        val accessedFieldType = inType.attrs.find(_.name == f) match {
            case Some(attr) => attr.tpe
            case None => raise(f"unhandled field access due to missing field $f in ${inType.prettyPrint} in MlirCodegen.bindToName()")
        }
        val retTypeFields = inType.attrs.map(field => s"\"${field.name}\": ${mlirType(field.tpe)}").mkString("record<", ", ", ">")

        val compE = bindToName(e, None)

        val binding = desired.getOrElse(fresh.next("%fieldnode"))

        val op = s"$binding = sdql.access_record ${compE.value} \"$f\" : $retTypeFields -> ${mlirType(accessedFieldType)} "

        Emitted(compE.code ++ Vector(op), binding)
      }

      // %0 = "func.call"(%1) <{callee = @range_builtin}> : (i32) -> dictionary<i32, i1>
      case RangeNode(e: Exp) => {
        val compE = bindToName(e, None)
        val binding = desired.getOrElse(fresh.next("%rangenode"))
        val typ = mlirType(TypeInference.run(e))

        val op = s"$binding = \"func.call\"(${compE.value}) <{callee = @range_builtin}> : ($typ) -> dictionary<$typ, i32>"
        Emitted(compE.code ++ Vector(op), binding)
      }


/* 
    %res = "scf.if"(%cond) ({
        %mul = "arith.mulf"(%l_extendedprice, %l_discount) <{"fastmath" = #arith.fastmath<none>}> : (f64, f64) -> f64
        "scf.yield"(%mul) : (f64) -> ()
    }, {
        %zero = "arith.constant"() <{value = 0.0 : f64}> : () -> f64
        "scf.yield"(%zero) : (f64) -> ()
    }) : (i1) -> f64
 */
      case IfThenElse(cond, thenp, elsep) => {
        val outT = mlirType(TypeInference.run(x))

        val c = bindToName(cond, None)
        val cTyp = mlirType(TypeInference.run(cond))

        val t = bindToName(thenp, None)
        val tTyp = mlirType(TypeInference.run(thenp))

        // val eTyp = mlirType(TypeInference.run(elsep))
        val e = bindToName(elsep, None, Some(TypeInference.run(x)))

        val binding = desired.getOrElse(fresh.next("%if"))
        val code = c.code ++
            Vector(s"$binding = \"scf.if\"(${c.value}) ({") ++
            t.code.map("  " + _) ++
            Vector(s"  \"scf.yield\"(${t.value}) : ($tTyp) -> ()") ++
            Vector("}, {") ++
            e.code.map("  " + _) ++
            Vector(s"  \"scf.yield\"(${e.value}) : (${tTyp}) -> ()") ++
            Vector(s"}) : ($cTyp) -> $outT")
        Emitted(code, binding)
      }
      
      case Cmp(e1, e2, cmp) if (e2.isInstanceOf[DictNode] && e2.asInstanceOf[DictNode].map == Nil) => {
        // is it always i1?
        val outT = mlirType(TypeInference.run(x))

        val predicateVal = cmp match {
          // https://mlir.llvm.org/docs/Dialects/ArithOps/#cmpfpredicate
          case "<=" => 5
          case "<" => 4
          case "!=" => 6
        }
        val comp1 = bindToName(e1, None)
        val type1 = TypeInference.run(e1)
        val t1 = mlirType(type1)
        val comp2 = bindToName(e2, None, Some(type1))
        val t2 = t1

        val binding = desired.getOrElse(fresh.next("%cmpf"))

        val op = s"$binding = \"arith.cmpf\"(${comp1.value}, ${comp2.value}) <{fastmath = #arith.fastmath<none>, predicate = $predicateVal}> : ($t1, $t2) -> $outT"
        Emitted(comp1.code ++ comp2.code ++ Vector(op), binding)
      }

      // %2 = "arith.cmpi"(%0, %1) <{predicate = 3}> : (i32, i32) -> i1
      case Cmp(e1, e2, cmp)
        if (TypeInference.run(e1) == IntType || TypeInference.run(e1) == LongType || TypeInference.run(e1) == DateType) &&
          (TypeInference.run(e2) == IntType || TypeInference.run(e2) == LongType || TypeInference.run(e2) == DateType) => {
          // is it always i1?
          val outT = mlirType(TypeInference.run(x))

          val predicateVal = cmp match {
            // https://mlir.llvm.org/docs/Dialects/ArithOps/#cmpipredicate
            case "<=" => 3
            case "<" => 2
            case "==" => 0
            case "!=" => 1
          }
          val comp1 = bindToName(e1, None)
          val t1 = mlirType(TypeInference.run(e1))
          val comp2 = bindToName(e2, None)
          val t2 = mlirType(TypeInference.run(e2))

          val binding = desired.getOrElse(fresh.next("%cmpi"))

          val op = s"$binding = \"arith.cmpi\"(${comp1.value}, ${comp2.value}) <{predicate = $predicateVal}> : ($t1, $t2) -> $outT"
          Emitted(comp1.code ++ comp2.code ++ Vector(op), binding)
        }

      case Cmp(e1, e2, cmp) if (TypeInference.run(e1) == RealType || TypeInference.run(e1) == RealType) => {
        // is it always i1?
        val outT = mlirType(TypeInference.run(x))

        val predicateVal = cmp match {
          // https://mlir.llvm.org/docs/Dialects/ArithOps/#cmpfpredicate
          case "<=" => 5
          case "<" => 4
          case "!=" => 6
          case "==" => 1
        }
        val comp1 = bindToName(e1, None)
        val t1 = mlirType(TypeInference.run(e1))
        val comp2 = bindToName(e2, None)
        val t2 = mlirType(TypeInference.run(e2))

        val binding = desired.getOrElse(fresh.next("%cmpf"))

        val op = s"$binding = \"arith.cmpf\"(${comp1.value}, ${comp2.value}) <{fastmath = #arith.fastmath<none>, predicate = $predicateVal}> : ($t1, $t2) -> $outT"
        Emitted(comp1.code ++ comp2.code ++ Vector(op), binding)
      }

      // %a = arith.muli %b, %c : i64
      case Mult(e1, e2)
        if (TypeInference.run(e1) == IntType || TypeInference.run(e1) == LongType) &&
          (TypeInference.run(e2) == IntType || TypeInference.run(e2) == LongType) => {
          val outT = mlirType(TypeInference.run(x))
          
          val binding = desired.getOrElse(fresh.next("%multi"))

          val comp1 = bindToName(e1, None)
          val t1 = mlirType(TypeInference.run(e1))
          val comp2 = bindToName(e2, None)
          val t2 = mlirType(TypeInference.run(e2))

          val op = s"$binding = \"arith.muli\"(${comp1.value}, ${comp2.value}) : ($t1, $t2) -> $outT"
          Emitted(comp1.code ++ comp2.code ++ Vector(op), binding)
      }

      case Mult(e1, e2) if TypeInference.run(e1) == RealType || TypeInference.run(e2) == RealType => {
          val outT = mlirType(TypeInference.run(x))
          
          val binding = desired.getOrElse(fresh.next("%multf"))

          val comp1 = bindToName(e1, None)
          val t1 = mlirType(TypeInference.run(e1))
          val comp2 = bindToName(e2, None)
          val t2 = mlirType(TypeInference.run(e2))

          val op = s"$binding = \"arith.mulf\"(${comp1.value}, ${comp2.value}) <{fastmath = #arith.fastmath<none>}> : ($t1, $t2) -> $outT"
          Emitted(comp1.code ++ comp2.code ++ Vector(op), binding)
      }

      case Add(e1, e2) if List(IntType, LongType).contains(TypeInference.run(e1)) => {
          val outT = mlirType(TypeInference.run(x))
          
          val binding = desired.getOrElse(fresh.next("%addi"))

          val comp1 = bindToName(e1, None)
          val t1 = mlirType(TypeInference.run(e1))
          val comp2 = bindToName(e2, None)
          val t2 = mlirType(TypeInference.run(e2))

          val op = s"$binding = \"arith.addi\"(${comp1.value}, ${comp2.value}) : ($t1, $t2) -> $outT"
          Emitted(comp1.code ++ comp2.code ++ Vector(op), binding)

      }

      case Add(e1, e2) if TypeInference.run(e1) == RealType => {
          val outT = mlirType(TypeInference.run(x))
          
          val binding = desired.getOrElse(fresh.next("%addf"))

          val comp1 = bindToName(e1, None)
          val t1 = mlirType(TypeInference.run(e1))
          val comp2 = bindToName(e2, None)
          val t2 = mlirType(TypeInference.run(e2))

          val op = s"$binding = \"arith.addf\"(${comp1.value}, ${comp2.value}) <{fastmath = #arith.fastmath<none>}> : ($t1, $t2) -> $outT"
          Emitted(comp1.code ++ comp2.code ++ Vector(op), binding)
      }

      case Neg(e) if TypeInference.run(e) == BoolType => {
        val zero = desired.getOrElse(fresh.next("%zero"))
        val zeroOp = s"$zero = \"arith.constant\"() <{value = 0 : i1}> : () -> i1"

        // val res = s"$binding = \"arith.constant\"() <{value = $v : i32}> : () -> i32"

        val binding = desired.getOrElse(fresh.next("%neg"))

        val comp = bindToName(e, None)
        val op = s"$binding = \"arith.cmpi\"(${comp.value}, $zero) <{predicate = 0}> : (i1, i1) -> i1"
        Emitted(comp.code ++ Vector(zeroOp, op), comp.value)
      }
      case Neg(e) if List(IntType, LongType).contains(TypeInference.run(e)) => {          
          val binding = desired.getOrElse(fresh.next("%addf"))

          val comp = bindToName(e, None)
          val t = mlirType(TypeInference.run(e))

          val zero = desired.getOrElse(fresh.next("%zero"))
          val zeroOp = s"$zero = \"arith.constant\"() <{value = 0 : $t}> : () -> $t"

          val op = s"$binding = \"arith.subi\"($zero, ${comp.value}) : ($t, $t) -> $t"
          Emitted(comp.code ++ Vector(zeroOp) ++ Vector(op), binding)
      }
      case Neg(e) if TypeInference.run(e) == RealType => {          
          val binding = desired.getOrElse(fresh.next("%addf"))

          val comp = bindToName(e, None)
          val t = mlirType(TypeInference.run(e))

          val zero = desired.getOrElse(fresh.next("%zero"))
          val zeroOp = s"$zero = \"arith.constant\"() <{value = 0 : $t}> : () -> $t"

          val op = s"$binding = \"arith.subf\"($zero, ${comp.value}) <{fastmath = #arith.fastmath<none>}> : ($t, $t) -> $t"
          Emitted(comp.code ++ Vector(zeroOp) ++ Vector(op), binding)
      }

      case Concat(e1, e2)
      if TypeInference.run(e1).isInstanceOf[RecordType] && TypeInference.run(e2).isInstanceOf[RecordType] => {
        val outT = TypeInference.run(x)

        val typ1 = mlirType(TypeInference.run(e1))
        val typ2 = mlirType(TypeInference.run(e2))

        val gen1 = bindToName(e1, None)
        val gen2 = bindToName(e2, None)

        val binding = desired.getOrElse(fresh.next("%concat"))

        val op = s"$binding = sdql.concat ${gen1.value}, ${gen2.value} : $typ1, $typ2 -> $outT"
        Emitted(gen1.code ++ gen2.code ++ Vector(op), binding)
      }

      case External(name, args) => {
        val outT = TypeInference.run(x)
        
        val generated = args.map(bindToName(_, None))
        val types = args.map(TypeInference.run)
        println(s"name=$name, types=$types")
        val binding = desired.getOrElse(fresh.next("%external"))

        val op = s"$binding = sdql.external $name, ${generated.map(_.value).mkString(", ")} : ${types.map(mlirType)}} : ${mlirType(outT)}"
        Emitted(generated.flatMap(_.code).toVector ++ Vector(op), binding)
      }

      case Cmp(e1, e2, cmp) if cmp == "==" => {
        val outT = TypeInference.run(x)

        val typ1 = mlirType(TypeInference.run(e1))
        val typ2 = e2 match {
            // workaround for `a != { }`
            case DictNode(Nil, _) => typ1
            case _ => mlirType(TypeInference.run(e2))
        }

        val gen1 = bindToName(e1, None)
        // workaround for a != { }
        val gen2 = bindToName(e2, None, expected = Some(TypeInference.run(e1)))

        val binding = desired.getOrElse(fresh.next("%cmp"))

        val op = s"$binding = sdql.cmp ${gen1.value}, ${gen2.value} : $typ1, $typ2 -> $outT"
        Emitted(gen1.code ++ gen2.code ++ Vector(op), binding)
      }

      case Cmp(e1, e2, cmp) if cmp == "!=" => {
        val negated = Cmp(e1, e2, "==")
        bindToName(Neg(negated), desired, expected)
      }

      case Unique(_) => {
        println("unique... " + TypeInference.run(x).prettyPrint)
        Emitted(Vector.empty, "")
      }

      case _ => {
        raise("¯\\_(ツ)_/¯ " + x)
      }
    }

    bindToName(e, None)(Map.empty)
  }
}
