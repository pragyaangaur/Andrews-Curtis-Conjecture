import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 447 of the cap-17 certificate: slots 228864 .. 229375 -/
theorem chk_447 : chunkCheck 17 T stdSt 228864 512 = true := by decide +kernel

end Row17
