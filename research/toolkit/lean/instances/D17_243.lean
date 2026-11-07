import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 243 of the cap-17 certificate: slots 124416 .. 124927 -/
theorem chk_243 : chunkCheck 17 T stdSt 124416 512 = true := by decide +kernel

end Row17
