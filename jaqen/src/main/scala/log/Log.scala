package log

import java.io.PrintWriter
import java.io.FileOutputStream

object Log {

  val out = new PrintWriter(new FileOutputStream("/Users/julien/macro.log", true), true)

  def apply(in: Any*) = {
    out.println(in.map(String.valueOf(_)).mkString(" "))
  }

}