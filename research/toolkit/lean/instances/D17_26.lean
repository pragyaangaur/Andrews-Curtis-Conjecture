import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 26 of the cap-17 certificate: slots 13312 .. 13823 -/
theorem chk_26 : chunkCheck 17 T stdSt 13312 512 = true := by decide +kernel

end Row17
