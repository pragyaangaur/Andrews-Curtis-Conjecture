import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 161 of the cap-17 certificate: slots 82432 .. 82943 -/
theorem chk_161 : chunkCheck 17 T stdSt 82432 512 = true := by decide +kernel

end Row17
