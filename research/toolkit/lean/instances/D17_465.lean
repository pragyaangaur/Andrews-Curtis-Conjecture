import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 465 of the cap-17 certificate: slots 238080 .. 238591 -/
theorem chk_465 : chunkCheck 17 T stdSt 238080 512 = true := by decide +kernel

end Row17
