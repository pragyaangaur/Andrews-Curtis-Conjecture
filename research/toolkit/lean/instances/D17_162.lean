import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 162 of the cap-17 certificate: slots 82944 .. 83455 -/
theorem chk_162 : chunkCheck 17 T stdSt 82944 512 = true := by decide +kernel

end Row17
