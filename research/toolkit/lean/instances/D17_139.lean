import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 139 of the cap-17 certificate: slots 71168 .. 71679 -/
theorem chk_139 : chunkCheck 17 T stdSt 71168 512 = true := by decide +kernel

end Row17
