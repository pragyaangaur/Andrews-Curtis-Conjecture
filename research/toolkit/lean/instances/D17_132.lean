import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 132 of the cap-17 certificate: slots 67584 .. 68095 -/
theorem chk_132 : chunkCheck 17 T stdSt 67584 512 = true := by decide +kernel

end Row17
