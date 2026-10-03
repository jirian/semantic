import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.*

/** A slice of a byte buffer. Writing to it is an `update`, so it is an exclusive capability. */
class Slice(private val data: Array[Byte]^, val start: Int, val end: Int) extends Mutable:
  def length: Int = end - start
  def read(i: Int): Byte = data(start + i)
  update def write(i: Int, b: Byte): Unit = data(start + i) = b
  update def fill(b: Byte): Unit =
    var i = start
    while i < end do { data(i) = b; i += 1 }

/** The two halves of a split, each an independently owned slice. */
class Halves(val fst: Slice^, val snd: Slice^)

object Slice:
  def alloc(n: Int): Slice^ = Slice(new Array[Byte](n), 0, n)

  /** Owned split: consumes `s` and returns two fresh, separate halves. This is the trusted
   *  primitive whose typing rule the Lean development proves sound (`HasType.split`). */
  def split(consume s: Slice^, n: Int): Halves^ =
    caps.unsafe.unsafeAssumeSeparate:
      Halves(Slice(s.data, s.start, s.start + n), Slice(s.data, s.start + n, s.end))

/** Runs two computations, which separation checking requires to be separate. */
def par(a: () => Unit, b: () => Unit): Unit = { a(); b() }

/** Hands a slice to the "kernel": consumes it. */
def send(consume s: Slice^): Unit = ()

/** The abstract's `process`: accepted. */
def process(consume buf: Slice^): Slice^ =
  val hs = Slice.split(buf, 4)
  val hdr: Slice^ = hs.fst
  val body: Slice^ = hs.snd
  par(() => hdr.write(0, 1), () => body.fill(0))
  send(body)
  hdr

@main def demo(): Unit =
  val hdr = process(Slice.alloc(16))
  println(hdr.read(0))
