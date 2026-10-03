import language.experimental.captureChecking
import language.experimental.separationChecking
def useParentAfterSplit(consume buf: Slice^): Unit =
  val hs = Slice.split(buf, 4)
  buf.fill(0) // error: buf was consumed by split
