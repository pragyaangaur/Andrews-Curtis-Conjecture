import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 73 of the cap-17 certificate: slots 37376 .. 37887 -/
theorem chk_73 : chunkCheck 17 T stdSt 37376 512 = true := by decide +kernel

end Row17
