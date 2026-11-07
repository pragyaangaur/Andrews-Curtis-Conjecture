import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 95 of the cap-16 certificate: slots 97280 .. 98303 -/
theorem chk_95 : chunkCheck 16 T stdSt 97280 1024 = true := by decide +kernel

end Row16
