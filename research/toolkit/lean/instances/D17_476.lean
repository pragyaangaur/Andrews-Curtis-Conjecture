import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 476 of the cap-17 certificate: slots 243712 .. 244223 -/
theorem chk_476 : chunkCheck 17 T stdSt 243712 512 = true := by decide +kernel

end Row17
