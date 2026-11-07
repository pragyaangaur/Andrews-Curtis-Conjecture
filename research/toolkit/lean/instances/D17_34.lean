import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 34 of the cap-17 certificate: slots 17408 .. 17919 -/
theorem chk_34 : chunkCheck 17 T stdSt 17408 512 = true := by decide +kernel

end Row17
