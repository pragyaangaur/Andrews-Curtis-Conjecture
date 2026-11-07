import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 222 of the cap-16 certificate: slots 227328 .. 228351 -/
theorem chk_222 : chunkCheck 16 T stdSt 227328 1024 = true := by decide +kernel

end Row16
