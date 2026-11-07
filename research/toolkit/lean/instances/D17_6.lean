import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 6 of the cap-17 certificate: slots 3072 .. 3583 -/
theorem chk_6 : chunkCheck 17 T stdSt 3072 512 = true := by decide +kernel

end Row17
