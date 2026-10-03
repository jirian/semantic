import language.experimental.captureChecking
import language.experimental.separationChecking
def useAfterSend(consume buf: Slice^): Unit =
  val hs = Slice.split(buf, 4)
  val body: Slice^ = hs.snd
  send(body)
  body.fill(0) // error: body was consumed by send
