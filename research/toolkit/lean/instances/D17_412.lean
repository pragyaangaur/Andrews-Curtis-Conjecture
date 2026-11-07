import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 412 of the cap-17 certificate: slots 210944 .. 211455 -/
theorem chk_412 : chunkCheck 17 T stdSt 210944 512 = true := by decide +kernel

end Row17
