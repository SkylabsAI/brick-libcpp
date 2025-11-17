# Shared Dune Caching across DevContainers

This container stores a dune cache on the host in `~/.cache/remote_dune`; this
is shared between different containers.

You can use `dune cache trim` commands inside a container to reduce its size, or
simply remove the folder from the host as desired, as long as containers are not
running.
