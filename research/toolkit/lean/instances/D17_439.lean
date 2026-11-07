import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 439 of the cap-17 certificate: slots 224768 .. 225279 -/
theorem chk_439 : chunkCheck 17 T stdSt 224768 512 = true := by decide +kernel

end Row17
