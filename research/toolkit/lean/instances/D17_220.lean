import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 220 of the cap-17 certificate: slots 112640 .. 113151 -/
theorem chk_220 : chunkCheck 17 T stdSt 112640 512 = true := by decide +kernel

end Row17
