package sdql
package driver

import sdql.backend.{ CppCodegen, CppCompile, Interpreter }
import sdql.frontend.*
import sdql.ir.*
import sdql.transformations.Rewriter

import java.nio.file.Path
import sdql.backend.MlirCodegen

object Main {
  def main(args: Array[String]): Unit = {
    if (args.length < 1) { raise("usage: `run <cmd> <args>*`") }
    args(0) match {
      case "interpret" =>
        if (args.length < 3) { raise("usage: `run interpret <path> <sdql_files>*`") }
        val dirPath   = Path.of(args(1))
        val fileNames = args.drop(2)
        for (fileName <- fileNames) {
          val filePath = dirPath.resolve(fileName)
          val prog     = SourceCode.fromFile(filePath.toString).exp
          val res      = Interpreter(prog)
          println(fileName)
          println({ Value.toString(res) })
          println()
        }
      case "compile"   =>
        if (args.length < 3) { raise("usage: `run compile <path> <sdql_files>*`") }
        val dirPath   = Path.of(args(1))
        val fileNames = args.drop(2)
        CppCompile.cmake(dirPath, fileNames)
        for (fileName <- fileNames) {
          val filePath = dirPath.resolve(fileName)
          val prog     = SourceCode.fromFile(filePath.toString).exp
          println("prog: " + prog)
          val procodegened = MlirCodegen.run(prog)
          println(procodegened.mkString("\n"))

          println(prog)
          val llql     = Rewriter.rewrite(prog)
          val res      = CppCodegen(llql)
          println(fileName)
          println(CppCompile.compile(filePath.toString, res))
          println()
        }
      case "to_mlir" =>
        if (args.length < 3) { raise("usage: `run to_mlir <path> <sdql_files>*`") }
        // val dirPath   = Path.of(args(1))
        // val fileNames = args.drop(2)
        // CppCompile.cmake(dirPath, fileNames)
        // for (_ <- fileNames) {
        // val filePath = dirPath.resolve(fileName)
        val q: Exp = LetBinding(Sym("dict"),
          // empty dictionary literal
          DictNode(Seq(
            Const(1) -> Const(2.0)   // { 1 -> 2.0 }
          ), PHmap(None)),
          LetBinding(Sym("key"),
            Const(1),
            // lookup
            Get(Sym("dict"), Sym("key"))
          )
        )
        val prog = MlirCodegen.run(q)
        println(prog.mkString("\n"))

        val q2: Exp =
          LetBinding(Sym("outer"),
            // outer : dictionary<i32, dictionary<i32, f64>>
            DictNode(Seq(
              // 1 -> { 10 -> 2.0, 20 -> 3.5 }
              Const(1) -> DictNode(Seq(
                Const(10) -> Const(2.0),
                Const(20) -> Const(3.5)
              ), PHmap(None)),

              // 3 -> { 30 -> 4.25 }
              Const(3) -> DictNode(Seq(
                Const(30) -> Const(4.25)
              ), PHmap(None))
            ), PHmap(None)),

            // body: look up outer[1][20]
            LetBinding(Sym("kOuter"), Const(1),
              LetBinding(Sym("kInner"), Const(20),
                LetBinding(Sym("inner"),
                  Get(Sym("outer"), Sym("kOuter")),     // inner = outer[kOuter]
                  Get(Sym("inner"), Sym("kInner"))      // result = inner[kInner]
                )
              )
            )
          )
          val prog2 = MlirCodegen.run(q2)
          println("\nprog2: ")
          println(prog2.mkString("\n"))
        // }
      case "benchmark" =>
        if (args.length < 4) { raise("usage: `run benchmark n <path> <sdql_files>*`") }
        val n         = args(1).toInt
        val dirPath   = Path.of(args(2))
        val fileNames = args.drop(3)
        for (fileName <- fileNames) {
          val filePath = dirPath.resolve(fileName)
          val prog     = SourceCode.fromFile(filePath.toString).exp
          val llql     = Rewriter.rewrite(prog)
          val res      = CppCodegen(llql, benchmarkRuns = n)
          CppCompile.writeFormat(filePath.toString, res)
        }
      case arg         => raise(s"`run $arg` not supported")
    }
  }
}
