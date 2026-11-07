import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 166 of the cap-17 certificate: slots 84992 .. 85503 -/
theorem chk_166 : chunkCheck 17 T stdSt 84992 512 = true := by decide +kernel

end Row17
