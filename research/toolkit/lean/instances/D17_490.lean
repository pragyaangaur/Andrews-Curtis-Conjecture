import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 490 of the cap-17 certificate: slots 250880 .. 251391 -/
theorem chk_490 : chunkCheck 17 T stdSt 250880 512 = true := by decide +kernel

end Row17
