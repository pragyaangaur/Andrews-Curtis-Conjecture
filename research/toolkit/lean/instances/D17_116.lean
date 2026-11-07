import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 116 of the cap-17 certificate: slots 59392 .. 59903 -/
theorem chk_116 : chunkCheck 17 T stdSt 59392 512 = true := by decide +kernel

end Row17
