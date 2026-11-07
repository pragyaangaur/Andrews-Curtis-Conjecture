import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 71 of the cap-17 certificate: slots 36352 .. 36863 -/
theorem chk_71 : chunkCheck 17 T stdSt 36352 512 = true := by decide +kernel

end Row17
