import language.experimental.captureChecking
import language.experimental.separationChecking
def splitBorrowed(buf: Slice^): Halves^ =
  Slice.split(buf, 4) // error: buf is borrowed, so it cannot be consumed
