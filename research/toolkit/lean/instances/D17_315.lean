import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 315 of the cap-17 certificate: slots 161280 .. 161791 -/
theorem chk_315 : chunkCheck 17 T stdSt 161280 512 = true := by decide +kernel

end Row17
