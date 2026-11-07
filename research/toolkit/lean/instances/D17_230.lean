import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 230 of the cap-17 certificate: slots 117760 .. 118271 -/
theorem chk_230 : chunkCheck 17 T stdSt 117760 512 = true := by decide +kernel

end Row17
