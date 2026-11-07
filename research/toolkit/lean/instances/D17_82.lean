import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 82 of the cap-17 certificate: slots 41984 .. 42495 -/
theorem chk_82 : chunkCheck 17 T stdSt 41984 512 = true := by decide +kernel

end Row17
