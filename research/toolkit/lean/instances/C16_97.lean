import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 97 of the cap-16 certificate: slots 99328 .. 100351 -/
theorem chk_97 : chunkCheck 16 T stdSt 99328 1024 = true := by decide +kernel

end Row16
