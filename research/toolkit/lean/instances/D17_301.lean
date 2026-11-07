import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 301 of the cap-17 certificate: slots 154112 .. 154623 -/
theorem chk_301 : chunkCheck 17 T stdSt 154112 512 = true := by decide +kernel

end Row17
