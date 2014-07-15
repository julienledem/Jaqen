package printexpr

import scala.reflect.macros.Context
import scala.language.experimental.macros
import log.Log

object PrintExpr {

  def printExpr(param: Any): Unit = macro impl

  def printParamType(param: Any): Unit = macro printParamTypeImpl

  def indent(level: Int): String = {
    (0 to level).foldLeft("")((agg, v) => "  " + agg)
  }

  def format(s: String) = {

      def indexOfDelim(s: String, delim: String): (Int, String) = (s.indexOf(delim), delim)

      def removeLeadingSpaces(s: String): String = if (s.startsWith(" ")) removeLeadingSpaces(s.substring(1)) else s

      def splitNextDelim(s: String) = {
        val delims = (List("(", ")", ",").map(indexOfDelim(s, _)).filter {
          case (index, delim) => index != -1
        }).sortBy {
          case (index, delim) => index
        }
        if (delims.isEmpty) None else {
          val (index, delim) = delims.head
          Some((delim, s.substring(0, index), removeLeadingSpaces(s.substring(index + 1))))
        }
      }

      def format0(agg: String, s: String, level: Int): String = {
        splitNextDelim(s) match {
          case None => agg + s
          case Some((delim, before, after)) => {
            delim match {
              case "(" => if (after.startsWith(")"))
                format0(agg + before + "()", after.substring(1), level)
              else
                format0(agg + before + "(\n" + indent(level + 1), after, level + 1)
              case ")" =>
                format0(agg + before + "\n" + indent(level - 1) + ")", after, level - 1)
              case "," =>
                format0(agg + before + ",\n" + indent(level), after, level)
            }
          }
        }
      }
      format0("", s, 0)
  }

  def impl(c: Context)(param: c.Expr[Any]): c.Expr[Unit] = {
    import c.universe._
    def lit(s: String) = c.Expr[String](Literal(Constant(s)))
    Log("<+++++++++")
    Log(format(showRaw(param.tree, true, false, true, false)))
    Log("-----------")
    param.tree match {
      case Block(
        List(
            ClassDef(
                _,
                _,
                _,
                Template(_, _, List(_, TypeDef(_,_,_,exp)))
            )
        ),
        _
      ) => Log(format(showRaw(exp))); Log(show(exp)); Log(format(showRaw(exp.tpe)))
      case _ =>
    }
    Log("+++++++++>")
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

