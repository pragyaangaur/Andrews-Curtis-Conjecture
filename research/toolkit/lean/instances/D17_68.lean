import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 68 of the cap-17 certificate: slots 34816 .. 35327 -/
theorem chk_68 : chunkCheck 17 T stdSt 34816 512 = true := by decide +kernel

end Row17
