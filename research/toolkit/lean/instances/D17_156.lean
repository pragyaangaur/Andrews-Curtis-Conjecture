import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 156 of the cap-17 certificate: slots 79872 .. 80383 -/
theorem chk_156 : chunkCheck 17 T stdSt 79872 512 = true := by decide +kernel

end Row17
