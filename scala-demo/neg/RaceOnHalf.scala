import language.experimental.captureChecking
import language.experimental.separationChecking
def raceOnHalf(consume buf: Slice^): Unit =
  val hs = Slice.split(buf, 4)
  val hdr: Slice^ = hs.fst
  par(() => hdr.fill(1), () => hdr.fill(2)) // error: the two branches are not separate
