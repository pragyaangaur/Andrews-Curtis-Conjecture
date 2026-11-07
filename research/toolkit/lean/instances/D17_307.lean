import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 307 of the cap-17 certificate: slots 157184 .. 157695 -/
theorem chk_307 : chunkCheck 17 T stdSt 157184 512 = true := by decide +kernel

end Row17
