# Module 59.6 Dynamic NVMe Loading

Defines the supported NVMe loading modes (ALL_IN_MEMORY, DYNAMIC_FFN_ONLY, DYNAMIC_ALL)
and connects them to dispatcher checks so users know when the runtime can swap weights
from storage.
