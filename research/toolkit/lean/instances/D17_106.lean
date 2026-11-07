import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 106 of the cap-17 certificate: slots 54272 .. 54783 -/
theorem chk_106 : chunkCheck 17 T stdSt 54272 512 = true := by decide +kernel

end Row17
