import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 241 of the cap-17 certificate: slots 123392 .. 123903 -/
theorem chk_241 : chunkCheck 17 T stdSt 123392 512 = true := by decide +kernel

end Row17
