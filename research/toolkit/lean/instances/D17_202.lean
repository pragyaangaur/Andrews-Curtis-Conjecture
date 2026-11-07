import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 202 of the cap-17 certificate: slots 103424 .. 103935 -/
theorem chk_202 : chunkCheck 17 T stdSt 103424 512 = true := by decide +kernel

end Row17
