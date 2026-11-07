import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 381 of the cap-17 certificate: slots 195072 .. 195583 -/
theorem chk_381 : chunkCheck 17 T stdSt 195072 512 = true := by decide +kernel

end Row17
