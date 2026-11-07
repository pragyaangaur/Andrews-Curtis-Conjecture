import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 39 of the cap-17 certificate: slots 19968 .. 20479 -/
theorem chk_39 : chunkCheck 17 T stdSt 19968 512 = true := by decide +kernel

end Row17
