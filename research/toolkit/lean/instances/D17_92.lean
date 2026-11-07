import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 92 of the cap-17 certificate: slots 47104 .. 47615 -/
theorem chk_92 : chunkCheck 17 T stdSt 47104 512 = true := by decide +kernel

end Row17
