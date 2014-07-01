package printexpr

import scala.reflect.macros.Context
import scala.language.experimental.macros

object PrintExpr {

  def printExpr(param: Any): Unit = macro impl

  def printParamType(param: Any): Unit = macro printParamTypeImpl

  def impl(c: Context)(param: c.Expr[Any]): c.Expr[Unit] = {
    import c.universe._
    def lit(s: String) = c.Expr[String](Literal(Constant(s)))
    reify {
      println("               param: " + lit(show(param.tree)).splice)
      println("           raw param: " + lit(showRaw(param.tree)).splice)
      println("raw param actualType: " + lit(showRaw(param.actualType)).splice)
    }
  }

  def printParamTypeImpl(c: Context)(param: c.Expr[Any]): c.Expr[Unit] = {
    import c.universe._

    def lit(s: Any) = c.Expr[String](Literal(Constant(showRaw(s))))

    val s2 = param.actualType match {
      case TypeRef(_, _, List(TypeRef(_, t1, _), TypeRef(_, t2, _))) => t2.toString()
    }
    reify {
      println("param.actualType raw: " + lit(param.actualType).splice)
      println(lit(s2).splice)
      println("param.actualType toString: " + lit(param.actualType.toString).splice)
//      println(param.splice)
//      println(lit(param.actualType.typeSymbol.toString).splice)
//      println(lit(param.actualType.widen.toString()).splice)
//      println(lit(param.staticType.toString()).splice)
//      println(lit(param.actualType.typeSymbol.typeSignature.toString).splice)
//      println(lit(param.actualType.termSymbol.typeSignature.toString).splice)
//      println(lit(param.actualType.baseClasses.toString).splice)
//      println(lit(param.actualType.typeConstructor.members.toString()).splice)
//      println(lit(param.actualType.declarations.toString).splice)
//      println(lit(param.actualType.getClass.toString).splice)
    }
  }

}

