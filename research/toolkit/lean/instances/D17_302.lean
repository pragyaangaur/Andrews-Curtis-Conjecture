import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 302 of the cap-17 certificate: slots 154624 .. 155135 -/
theorem chk_302 : chunkCheck 17 T stdSt 154624 512 = true := by decide +kernel

end Row17
