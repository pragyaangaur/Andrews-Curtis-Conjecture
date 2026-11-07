import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 421 of the cap-17 certificate: slots 215552 .. 216063 -/
theorem chk_421 : chunkCheck 17 T stdSt 215552 512 = true := by decide +kernel

end Row17
