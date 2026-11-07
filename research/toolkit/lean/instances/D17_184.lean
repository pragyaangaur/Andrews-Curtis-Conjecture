import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 184 of the cap-17 certificate: slots 94208 .. 94719 -/
theorem chk_184 : chunkCheck 17 T stdSt 94208 512 = true := by decide +kernel

end Row17
