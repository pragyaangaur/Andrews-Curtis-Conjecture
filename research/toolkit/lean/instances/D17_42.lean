import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 42 of the cap-17 certificate: slots 21504 .. 22015 -/
theorem chk_42 : chunkCheck 17 T stdSt 21504 512 = true := by decide +kernel

end Row17
