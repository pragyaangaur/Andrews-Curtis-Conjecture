import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 20 of the cap-17 certificate: slots 10240 .. 10751 -/
theorem chk_20 : chunkCheck 17 T stdSt 10240 512 = true := by decide +kernel

end Row17
