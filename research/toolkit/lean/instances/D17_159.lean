import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 159 of the cap-17 certificate: slots 81408 .. 81919 -/
theorem chk_159 : chunkCheck 17 T stdSt 81408 512 = true := by decide +kernel

end Row17
