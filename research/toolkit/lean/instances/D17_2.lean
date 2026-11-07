import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 2 of the cap-17 certificate: slots 1024 .. 1535 -/
theorem chk_2 : chunkCheck 17 T stdSt 1024 512 = true := by decide +kernel

end Row17
