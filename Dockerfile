FROM rust:buster
RUN echo "deb https://dl.bintray.com/souffle-lang/deb buster main" >> /etc/apt/sources.list; \
    apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv-keys 379CE192D401AB61; \
    apt-get update; \
    apt-get --yes install souffle; \
    true;
