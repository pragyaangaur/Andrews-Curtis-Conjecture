import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 310 of the cap-17 certificate: slots 158720 .. 159231 -/
theorem chk_310 : chunkCheck 17 T stdSt 158720 512 = true := by decide +kernel

end Row17
