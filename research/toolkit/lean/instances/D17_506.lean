import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 506 of the cap-17 certificate: slots 259072 .. 259583 -/
theorem chk_506 : chunkCheck 17 T stdSt 259072 512 = true := by decide +kernel

end Row17
