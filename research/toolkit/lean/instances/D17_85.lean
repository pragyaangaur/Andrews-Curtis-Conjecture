import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 85 of the cap-17 certificate: slots 43520 .. 44031 -/
theorem chk_85 : chunkCheck 17 T stdSt 43520 512 = true := by decide +kernel

end Row17
