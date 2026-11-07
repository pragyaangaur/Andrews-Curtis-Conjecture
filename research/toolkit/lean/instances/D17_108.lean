import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 108 of the cap-17 certificate: slots 55296 .. 55807 -/
theorem chk_108 : chunkCheck 17 T stdSt 55296 512 = true := by decide +kernel

end Row17
