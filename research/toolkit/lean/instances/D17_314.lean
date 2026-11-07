import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 314 of the cap-17 certificate: slots 160768 .. 161279 -/
theorem chk_314 : chunkCheck 17 T stdSt 160768 512 = true := by decide +kernel

end Row17
