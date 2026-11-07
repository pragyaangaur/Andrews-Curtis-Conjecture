import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 448 of the cap-17 certificate: slots 229376 .. 229887 -/
theorem chk_448 : chunkCheck 17 T stdSt 229376 512 = true := by decide +kernel

end Row17
