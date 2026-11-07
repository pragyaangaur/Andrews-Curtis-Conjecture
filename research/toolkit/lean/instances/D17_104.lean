import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 104 of the cap-17 certificate: slots 53248 .. 53759 -/
theorem chk_104 : chunkCheck 17 T stdSt 53248 512 = true := by decide +kernel

end Row17
